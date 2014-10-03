#include "userprog/syscall.h"
#include <stdio.h>
#include <string.h>
#include <syscall-nr.h>
#include "userprog/process.h"
#include "userprog/pagedir.h"
#include "devices/input.h"
#include "devices/shutdown.h"
#include "filesys/filesys.h"
#include "filesys/file.h"
#include "threads/interrupt.h"
#include "threads/malloc.h"
#include "threads/palloc.h"
#include "threads/thread.h"
#include "threads/vaddr.h"

static int sys_halt (void);
static int sys_exit (int status);
static int sys_exec (const char *ufile);
static int sys_wait (tid_t);
static int sys_create (const char *ufile, unsigned initial_size);
static int sys_remove (const char *ufile);
static int sys_open (const char *ufile);
static int sys_filesize (int handle);
static int sys_read (int handle, void *udst_, unsigned size);
static int sys_write (int handle, void *usrc_, unsigned size);
static int sys_seek (int handle, unsigned position);
static int sys_tell (int handle);
static int sys_close (int handle);

static void syscall_handler (struct intr_frame *);
static void copy_in (void *, const void *, size_t);

/* Serializes file system operations. */
static struct lock fs_lock;

/* Initialize the system call system, called by the init process
   when the system starts.
   What we do here is to register an interrupt handler, i.e. syscall_handler,
   that captures software interrupt issued while making a system call.
 */
void
syscall_init (void)
{
  intr_register_int (0x30, 3, INTR_ON, syscall_handler, "syscall");

  /* Initialize a file system lock here. This lock is used to synchronize
     the access to the file system since the file system does not support concurrent
     access at the moment. */
  lock_init (&fs_lock);
}

/* System call handler. */
static void
syscall_handler (struct intr_frame *f)
{
  typedef int syscall_function (int, int, int);

  /* A system call. */
  struct syscall
    {
      size_t arg_cnt;           /* Number of arguments. */
      syscall_function *func;   /* Implementation. */
    };

  /* Table of system calls. */
  /* First number on each row refers to the number of arguments.
     second number on each row is a pointer to the corresponding syscall
     function. */
  static const struct syscall syscall_table[] =
    {
      {0, (syscall_function *) sys_halt},
      {1, (syscall_function *) sys_exit},
      {1, (syscall_function *) sys_exec},
      {1, (syscall_function *) sys_wait},
      {2, (syscall_function *) sys_create},
      {1, (syscall_function *) sys_remove},
      {1, (syscall_function *) sys_open},
      {1, (syscall_function *) sys_filesize},
      {3, (syscall_function *) sys_read},
      {3, (syscall_function *) sys_write},
      {2, (syscall_function *) sys_seek},
      {1, (syscall_function *) sys_tell},
      {1, (syscall_function *) sys_close},
    };

  const struct syscall *sc;
  unsigned call_nr;
  int args[3];

  /* Get the system call. */
  /* The system call number is stored in the caller's stack.
       we can use the stack pointer to retrieve the call number. */
  copy_in (&call_nr, f->esp, sizeof call_nr);
  if (call_nr >= sizeof syscall_table / sizeof *syscall_table)
    thread_exit ();

  /* sc contains the address of the requested syscall
     structure that contains the number of arguments and the
     corresponding function pointer. note that the calculation
     below implies that the there is an one-to-one mapping between
     system call number and the call function given in the system
     call table. The order of system call function in the system
     call table cannot be changed arbitrarily. */
  sc = syscall_table + call_nr;

  /* Get the system call arguments. */
  /* notice that the argument array args must be able
      to hold all arguments requested by the system call. */
  ASSERT (sc->arg_cnt <= sizeof args / sizeof *args);
  memset (args, 0, sizeof args);

  /* Copy all system call arguments from user's stack
      into the argument array args. Notice that the element
      at the top of the stack is the call number. This element
      has to be omitted from the copying (i.e. esp+1). */
  copy_in (args, (uint32_t *) f->esp + 1, (sizeof *args) * sc->arg_cnt);

  /* Execute the system call, and set the return value. */
  /* note that the system call return result will be kept
      in eax member of the struct intr_frame. */
  f->eax = sc->func (args[0], args[1], args[2]);
}

/* Returns true if UADDR is a valid, mapped user address,
   false otherwise. */
static bool
verify_user (const void *uaddr)
{
  return (uaddr < PHYS_BASE
          && pagedir_get_page (thread_current ()->pagedir, uaddr) != NULL);
}

/* Copies a byte from user address USRC to kernel address DST.
   USRC must be below PHYS_BASE.
   Returns true if successful, false if a segfault occurred. */
static inline bool get_user (uint8_t *dst, const uint8_t *usrc)
{
  int eax;
  asm ("movl $1f, %%eax; movb %2, %%al; movb %%al, %0; 1:"
       : "=m" (*dst), "=&a" (eax) : "m" (*usrc));
  return eax != 0;
}

/* Writes BYTE to user address UDST.
   UDST must be below PHYS_BASE.
   Returns true if successful, false if a segfault occurred. */
static inline bool put_user (uint8_t *udst, uint8_t byte)
{
  int eax;
  asm ("movl $1f, %%eax; movb %b2, %0; 1:"
       : "=m" (*udst), "=&a" (eax) : "q" (byte));
  return eax != 0;
}

/* Copies SIZE bytes from user address USRC to kernel address
   DST.
   Call thread_exit() if any of the user accesses are invalid. */
static void copy_in (void *dst_, const void *usrc_, size_t size)
{
  uint8_t *dst = dst_;
  const uint8_t *usrc = usrc_;

  for (; size > 0; size--, dst++, usrc++)
    if (usrc >= (uint8_t *) PHYS_BASE || !get_user (dst, usrc))
      thread_exit ();
}

/* Creates a copy of user string US in kernel memory
   and returns it as a page that must be freed with
   palloc_free_page().
   Truncates the string at PGSIZE bytes in size.
   Call thread_exit() if any of the user accesses are invalid. */
static char * copy_in_string (const char *us)
{
  char *ks;
  size_t length;

  /* NOTE: argument 0 here means to simply return a kernel page if available. */
  ks = palloc_get_page (0);
  if (ks == NULL)
    thread_exit ();

  for (length = 0; length < PGSIZE; length++)
    {
      if (us >= (char *) PHYS_BASE || !get_user (ks + length, us++))
        {
          palloc_free_page (ks);
          thread_exit ();
        }

      if (ks[length] == '\0')
        return ks;
    }

  /* The following applies to the case when the string to copied
     is larger than PGSIZE. In this case, we will never copy '\0' into the
     newly allocated kernel page in the above for loop. So the last byte
     of the kernel page must be set to '\0' to truncate the string being
     copied. */
  ks[PGSIZE - 1] = '\0';
  return ks;
}

/* Halt system call. */
static int sys_halt (void)
{
    printf ("system call!\n");
    //thread_exit ();
     shutdown_power_off();
}

/* Exit system call. */
static int sys_exit(int exit_code) {
    thread_current()->wait_status->exit_code = exit_code;
    thread_exit();
    NOT_REACHED();
}


/* Exec system call. */
static int sys_exec (const char *ufile)
{
    //Starts the execution of a user program and returns a valid PID of 
    //the child process if successful
    tid_t tid;
    char *new_file = copy_in_string(ufile);
    lock_acquire(&fs_lock);
    tid = process_execute(new_file);
    lock_release(&fs_lock);
    palloc_free_page(new_file);
    return tid;
}

/* Wait system call. */
static int sys_wait (tid_t child)
{
  
  //Waits for a child process and retrieves the child's exit value
    return process_wait(child);
}

/* Create system call. */
static int sys_create (const char *ufile, unsigned initial_size)
{
  //Creates a new file and returns true if successful and false 
  //otherwise
    char *new_file = copy_in_string(ufile);
    bool success;
    lock_acquire(&fs_lock);
    success = filesys_create(new_file, initial_size);
    lock_release(&fs_lock);
    palloc_free_page(new_file);
    return success;
}

/* Remove system call. */
static int sys_remove (const char *ufile)
{
  //Deletes a file and returns true if successful and false otherwise
    char *new_file = copy_in_string(ufile);
    
    lock_acquire(&fs_lock);
    bool success = filesys_remove(new_file);
    lock_release(&fs_lock);
    palloc_free_page(new_file);
    return success;
}

/* A file descriptor, for binding a file handle to a file. */
struct file_descriptor
  {
    struct list_elem elem;      /* List element. */
    struct file *file;          /* File. */
    int handle;                 /* File handle. */
  };

/* Open system call. */
static int sys_open (const char *ufile)
{
  //opens a file and returns the corresponding file descriptor
    char *new_file = copy_in_string(ufile);
    struct file_descriptor *file;
    int reserved = -1;
    file = malloc(sizeof *file);
    
    if(file !=NULL){
      lock_acquire(&fs_lock);
      file->file = filesys_open(new_file);
      if(file->file !=NULL){
	struct thread *c = thread_current();
	reserved = file->handle = (c->next_handle+=1);
	list_push_front(&c->fds, &file->elem);
	
      }
      else{
	free(file);
      }
      lock_release(&fs_lock);
    }
    
    palloc_free_page(new_file);
    
    //printf ("system call!\n");
    //thread_exit ();
    return reserved;
}


// Returns the file descriptor associated with the given handle.

static struct file_descriptor *lookup_file(int handle) {
	struct thread *cur = thread_current();
	struct list_elem *element;

	for (element = list_begin(&cur->fds); element != list_end(&cur->fds); element = list_next(element)) {
		struct file_descriptor *fd;
		fd = list_entry (element, struct file_descriptor, elem);
		if (fd->handle == handle){
			return fd;
		}
	}

	thread_exit();
}


/* Filesize system call. */
static int sys_filesize (int handle)
{
  // Returns the size, in bytes, of a file
  int h = handle;
    struct file_descriptor *file = lookup_file(h);
    
    lock_acquire(&fs_lock);
    int size = file_length(file->file);
    lock_release(&fs_lock);
    
    
    return size;
}

/* Read system call. */
static int sys_read (int handle, void *udst_, unsigned size)
{
  uint8_t *udst = udst_;
  int bytes_read = 0;

  //my code
  struct file_descriptor *file;
  int h = handle;
  /* Handle keyboard reads. */
  if (handle == STDIN_FILENO)
  {
      /* the kernel function input_getc() is used to get a character from the
          standard input, i.e. the keyboard. */
      for (bytes_read = 0; (size_t) bytes_read < size; bytes_read++){
        if (udst >= (uint8_t *) PHYS_BASE || !put_user (udst++, input_getc ())){
          thread_exit ();
	}
      }
      return bytes_read;
  }
  else
  {
      //read a number of bytes from an open file into a buffer in the user program
      //return the number of bytes actually read, or -1 if the file could not be read
      file = lookup_file(h);
      lock_acquire(&fs_lock);
      
      while(size>=1){
	size_t page = PGSIZE-pg_ofs(udst);
	size_t read = size<page?size:page;
	off_t return_value;
	
	if(!verify_user(udst)){
	  lock_release(&fs_lock);
	  thread_exit();
	}
	
	return_value = file_read(file->file, udst, read);
	if(return_value<=1){
	  if(bytes_read == 0){
	    bytes_read = -1;
	    
	  }
	  break;
	}
	bytes_read = bytes_read + return_value;
	off_t value = (off_t)read;
	if(return_value != value){
	  break;
	}
	
	udst = udst + return_value;
	size = size - return_value;
	
      }
      
      lock_release(&fs_lock);
      
    
    
    //printf ("system call!\n");
      return bytes_read;
  }

  
}

/* Write system call. */
static int sys_write (int handle, void *usrc_, unsigned size)
{
  uint8_t *usrc = usrc_;
  int bytes_written = 0;

  //my code
  struct file_descriptor *file;
  int h = handle;
  
  
  /* Lookup up file descriptor. */
  if (handle != STDOUT_FILENO)
  {
      file = lookup_file(h);
    //printf ("system call!\n");
      //thread_exit ();
  }

  lock_acquire (&fs_lock);
  while (size > 0)
  {
      /* How many bytes to write to this page? */
      size_t page_left = PGSIZE - pg_ofs (usrc);
      size_t write_amt = size < page_left ? size : page_left;
      off_t retval;

      /* Check that we can touch this user page. */
      if (!verify_user (usrc))
      {
          lock_release (&fs_lock);
          thread_exit ();
      }

      /* Do the write on the standard output. */
      if(h==STDOUT_FILENO){
      putbuf (usrc, write_amt);
      retval = write_amt;
      }
      else{
	retval = file_write(file->file, usrc, write_amt);
      }
      if(retval<=1){
	if(bytes_written==0){
	  bytes_written = -1;
	}
	break;
      }
      bytes_written += retval;

      
	off_t value = (off_t)write_amt;
	if(retval != value){
	  break;
	}
      
      /* Advance. */
      usrc += retval;
      size -= retval;
  }
  lock_release (&fs_lock);

  return bytes_written;
}

/* Seek system call. */
static int sys_seek (int handle, unsigned position)
{
  int h = handle;
  struct file_descriptor *file = lookup_file(h);

  lock_acquire(&fs_lock);
  off_t p = (off_t)position;
  if(p>=0){
    file_seek(file->file, position);
  }
  lock_release(&fs_lock);
  
  
  //printf ("system call!\n");
    //thread_exit ();
    return 0;
}

/* Tell system call. */
static int sys_tell (int handle)
{
  unsigned p;
  int h = handle;
  struct file_descriptor *file = lookup_file(h);
  
  lock_acquire(&fs_lock);
  p = file_tell(file->file);
  lock_release(&fs_lock);
  //printf ("system call!\n");
    //thread_exit ();
    return p;
}

/* Close system call. */
static int sys_close (int handle)
{
    int h = handle;
    
    struct file_descriptor *file = lookup_file(h);
    lock_acquire(&fs_lock);
    file_close(file->file);
    lock_release(&fs_lock);
    list_remove(&file->elem);
    //printf ("system call!\n");
    //thread_exit ();
    free(file);
    return 0;
}

/* On thread exit, close all open files. */
void syscall_exit (void)
{
  struct thread *cur = thread_current ();
  struct list_elem *e, *next;

  for (e = list_begin (&cur->fds); e != list_end (&cur->fds); e = next)
    {
      struct file_descriptor *fd;
      fd = list_entry (e, struct file_descriptor, elem);
      next = list_next (e);
      lock_acquire (&fs_lock);
      file_close (fd->file);
      lock_release (&fs_lock);
      free (fd);
    }
}

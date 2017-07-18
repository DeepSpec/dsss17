; ModuleID = 'factorial64.c'
@.str = private unnamed_addr constant [21 x i8] c"factorial(6) = %llu\0A\00"

; Function Attrs: nounwind ssp
define i64 @factorial(i64 %n) #0 {
  %1 = alloca i64
  %acc = alloca i64
  store i64 %n, i64* %1
  store i64 1, i64* %acc
  br label %loop

loop:
  %3 = load i64* %1
  %4 = icmp sgt i64 %3, 0
  br i1 %4, label %body, label %post

body:
  %6 = load i64* %acc
  %7 = load i64* %1
  %8 = mul nsw i64 %6, %7
  store i64 %8, i64* %acc
  %9 = load i64* %1
  %10 = sub nsw i64 %9, 1
  store i64 %10, i64* %1
  br label %loop

post:
  %12 = load i64* %acc
  ret i64 %12
}

; Function Attrs: nounwind ssp
define i32 @main(i32 %argc, i8** %argv) {
  %1 = alloca i32
  %2 = alloca i8**
  store i32 %argc, i32* %1
  store i8** %argv, i8*** %2
  %3 = call i64 @factorial(i64 6)
  %4 = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([21 x i8]* @.str, i32 0, i32 0), i64 %3)
  ret i32 0
}

declare i32 @printf(i8*, ...) 


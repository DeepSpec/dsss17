; ModuleID = 'factorial64.c'
source_filename = "factorial64.c"
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.12.0"

@.str = private unnamed_addr constant [21 x i8] c"factorial(6) = %llu\0A\00", align 1

; Function Attrs: norecurse nounwind readnone ssp
define i64 @factorial(i64) local_unnamed_addr #0 {
  %2 = icmp sgt i64 %0, 0
  br i1 %2, label %3, label %11

; <label>:3:                                      ; preds = %1
  br label %4

; <label>:4:                                      ; preds = %3, %4
  %5 = phi i64 [ %7, %4 ], [ 1, %3 ]
  %6 = phi i64 [ %8, %4 ], [ %0, %3 ]
  %7 = mul nsw i64 %5, %6
  %8 = add nsw i64 %6, -1
  %9 = icmp sgt i64 %6, 1
  br i1 %9, label %4, label %10

; <label>:10:                                     ; preds = %4
  br label %11

; <label>:11:                                     ; preds = %10, %1
  %12 = phi i64 [ 1, %1 ], [ %7, %10 ]
  ret i64 %12
}

; Function Attrs: nounwind ssp
define i32 @main(i32, i8** nocapture readnone) local_unnamed_addr #1 {
  %3 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([21 x i8], [21 x i8]* @.str, i64 0, i64 0), i64 720)
  ret i32 0
}

; Function Attrs: nounwind
declare i32 @printf(i8* nocapture readonly, ...) local_unnamed_addr #2

attributes #0 = { norecurse nounwind readnone ssp "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind ssp "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"PIC Level", i32 2}
!1 = !{!"Apple LLVM version 8.1.0 (clang-802.0.42)"}

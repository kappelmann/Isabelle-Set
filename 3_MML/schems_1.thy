theory schems_1
  imports "../mizar_extension/E_fraenkel"
begin
(*begin*)
reserve a, b, d for "setHIDDENM2"
theorem schems_1_sch_1:
  fixes Pp1 
  assumes
    A1: " for a be setHIDDENM2 holds Pp1(a)"
  shows " ex a be setHIDDENM2 st Pp1(a)"
sorry

theorem schems_1_sch_2:
  fixes Sp2 
  assumes
    A1: " ex a be setHIDDENM2 st  for b be setHIDDENM2 holds Sp2(a,b)"
  shows " for b be setHIDDENM2 holds  ex a be setHIDDENM2 st Sp2(a,b)"
sorry

theorem schems_1_sch_3:
  fixes Pp1 Qp1 
  assumes
    A1: " for a be setHIDDENM2 holds Pp1(a) implies Qp1(a)"
  shows "( for a be setHIDDENM2 holds Pp1(a)) implies ( for a be setHIDDENM2 holds Qp1(a))"
sorry

theorem schems_1_sch_4:
  fixes Pp1 Qp1 
  assumes
    A1: " for a be setHIDDENM2 holds Pp1(a) iff Qp1(a)"
  shows "( for a be setHIDDENM2 holds Pp1(a)) iff ( for a be setHIDDENM2 holds Qp1(a))"
sorry

theorem schems_1_sch_5:
  fixes Pp1 Tp0 
  assumes
    A1: " for a be setHIDDENM2 holds Pp1(a) implies Tp0"
  shows "( for a be setHIDDENM2 holds Pp1(a)) implies Tp0"
sorry

theorem schems_1_sch_6:
  fixes Pp1 Qp1 
  assumes
    A1: "( ex a be setHIDDENM2 st Pp1(a)) or ( for b be setHIDDENM2 holds Qp1(b))"
  shows " ex a be setHIDDENM2 st  for b be setHIDDENM2 holds Pp1(a) or Qp1(b)"
sorry

theorem schems_1_sch_7:
  fixes Pp1 Qp1 
  assumes
    A1: " ex a be setHIDDENM2 st  for b be setHIDDENM2 holds Pp1(a) or Qp1(b)"
  shows "( ex a be setHIDDENM2 st Pp1(a)) or ( for b be setHIDDENM2 holds Qp1(b))"
sorry

theorem schems_1_sch_8:
  fixes Pp1 Qp1 
  assumes
    A1: " for b be setHIDDENM2 holds  ex a be setHIDDENM2 st Pp1(a) or Qp1(b)"
  shows " ex a be setHIDDENM2 st  for b be setHIDDENM2 holds Pp1(a) or Qp1(b)"
sorry

theorem schems_1_sch_9:
  fixes Pp1 Qp1 
  assumes
    A1: "( ex a be setHIDDENM2 st Pp1(a)) & ( for b be setHIDDENM2 holds Qp1(b))"
  shows " for b be setHIDDENM2 holds  ex a be setHIDDENM2 st Pp1(a) & Qp1(b)"
sorry

theorem schems_1_sch_10:
  fixes Pp1 Qp1 
  assumes
    A1: " for b be setHIDDENM2 holds  ex a be setHIDDENM2 st Pp1(a) & Qp1(b)"
  shows "( ex a be setHIDDENM2 st Pp1(a)) & ( for b be setHIDDENM2 holds Qp1(b))"
sorry

theorem schems_1_sch_11:
  fixes Pp1 Qp1 
  assumes
    A1: " for b be setHIDDENM2 holds  ex a be setHIDDENM2 st Pp1(a) & Qp1(b)"
  shows " ex a be setHIDDENM2 st  for b be setHIDDENM2 holds Pp1(a) & Qp1(b)"
sorry

theorem schems_1_sch_12:
  fixes Sp2 
  assumes
    A1: " for a be setHIDDENM2 holds  for b be setHIDDENM2 holds Sp2(a,b)"
  shows " ex b be setHIDDENM2 st  for a be setHIDDENM2 holds Sp2(a,b)"
sorry

theorem schems_1_sch_13:
  fixes Sp2 
  assumes
    A1: " ex a be setHIDDENM2 st  for b be setHIDDENM2 holds Sp2(a,b)"
  shows " ex a be setHIDDENM2 st Sp2(a,a)"
sorry

theorem schems_1_sch_14:
  fixes Sp2 
  assumes
    A1: " for a be setHIDDENM2 holds Sp2(a,a)"
  shows " for a be setHIDDENM2 holds  ex b be setHIDDENM2 st Sp2(b,a)"
sorry

theorem schems_1_sch_15:
  fixes Sp2 
  assumes
    A1: " for a be setHIDDENM2 holds Sp2(a,a)"
  shows " for a be setHIDDENM2 holds  ex b be setHIDDENM2 st Sp2(a,b)"
sorry

theorem schems_1_sch_16:
  fixes Sp2 
  assumes
    A1: " for b be setHIDDENM2 holds  ex a be setHIDDENM2 st Sp2(a,b)"
  shows " ex a be setHIDDENM2 st  ex b be setHIDDENM2 st Sp2(a,b)"
sorry

end

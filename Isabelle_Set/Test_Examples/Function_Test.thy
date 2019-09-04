theory Function_Test
imports "../String" "../Function"

begin


lemma test1: "{\<langle>x, y\<rangle>} `x = y"
  apply (rule apply_function, auto)
  done

lemma test2: "{\<langle>@x1, @y1\<rangle>, \<langle>@x2, @y2\<rangle>} `@x1 = @y1"
  apply (rule apply_function, auto)
  apply (rule cons_functionI, strings)+
  done

lemma test2': "{\<langle>@x1, @y1\<rangle>, \<langle>@x2, @y2\<rangle>} `@x2 = @y2"
  apply (rule apply_function, auto)
  apply (rule cons_functionI, strings)+
  done

thm apply_function

lemma test3: "{\<langle>@x1, @y1\<rangle>, \<langle>@x2, @y2\<rangle>, \<langle>@x3, @y3\<rangle>} `@x2 = @y2"
  apply (rule apply_function, auto)
  apply (rule cons_functionI, strings)+
  done

end

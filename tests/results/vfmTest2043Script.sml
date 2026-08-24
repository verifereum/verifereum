Theory vfmTest2043[no_sig_docs]
Ancestors vfmTestDefs2043
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2043_0.nsv", "result2043_1.nsv", "result2043_2.nsv", "result2043_3.nsv"];
val thyn = "vfmTestDefs2043";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

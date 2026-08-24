Theory vfmTest2745[no_sig_docs]
Ancestors vfmTestDefs2745
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2745_0.nsv", "result2745_1.nsv", "result2745_2.nsv", "result2745_3.nsv"];
val thyn = "vfmTestDefs2745";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

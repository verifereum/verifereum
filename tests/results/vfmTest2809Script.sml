Theory vfmTest2809[no_sig_docs]
Ancestors vfmTestDefs2809
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2809_0.nsv", "result2809_1.nsv", "result2809_2.nsv", "result2809_3.nsv"];
val thyn = "vfmTestDefs2809";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

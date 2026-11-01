Theory vfmTest2965[no_sig_docs]
Ancestors vfmTestDefs2965
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2965_0.nsv", "result2965_1.nsv", "result2965_2.nsv"];
val thyn = "vfmTestDefs2965";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

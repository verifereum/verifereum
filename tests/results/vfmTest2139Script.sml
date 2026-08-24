Theory vfmTest2139[no_sig_docs]
Ancestors vfmTestDefs2139
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2139_0.nsv"];
val thyn = "vfmTestDefs2139";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

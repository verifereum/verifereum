Theory vfmTest1909[no_sig_docs]
Ancestors vfmTestDefs1909
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1909_0.nsv", "result1909_1.nsv"];
val thyn = "vfmTestDefs1909";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

Theory vfmTest1991[no_sig_docs]
Ancestors vfmTestDefs1991
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1991_0.nsv", "result1991_1.nsv"];
val thyn = "vfmTestDefs1991";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

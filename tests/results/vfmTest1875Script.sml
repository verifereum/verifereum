Theory vfmTest1875[no_sig_docs]
Ancestors vfmTestDefs1875
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1875_0.nsv", "result1875_1.nsv"];
val thyn = "vfmTestDefs1875";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

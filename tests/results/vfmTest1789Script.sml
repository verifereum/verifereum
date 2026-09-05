Theory vfmTest1789[no_sig_docs]
Ancestors vfmTestDefs1789
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1789_0.nsv", "result1789_1.nsv", "result1789_2.nsv"];
val thyn = "vfmTestDefs1789";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

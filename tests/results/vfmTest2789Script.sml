Theory vfmTest2789[no_sig_docs]
Ancestors vfmTestDefs2789
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2789_0.nsv", "result2789_1.nsv", "result2789_2.nsv", "result2789_3.nsv"];
val thyn = "vfmTestDefs2789";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

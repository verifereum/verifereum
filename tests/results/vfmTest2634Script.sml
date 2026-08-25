Theory vfmTest2634[no_sig_docs]
Ancestors vfmTestDefs2634
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2634_0.nsv", "result2634_1.nsv", "result2634_2.nsv", "result2634_3.nsv"];
val thyn = "vfmTestDefs2634";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

Theory vfmTest2686[no_sig_docs]
Ancestors vfmTestDefs2686
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2686_0.nsv", "result2686_1.nsv", "result2686_2.nsv", "result2686_3.nsv"];
val thyn = "vfmTestDefs2686";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

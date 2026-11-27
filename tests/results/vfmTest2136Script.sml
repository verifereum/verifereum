Theory vfmTest2136[no_sig_docs]
Ancestors vfmTestDefs2136
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2136_0.nsv", "result2136_1.nsv", "result2136_2.nsv", "result2136_3.nsv", "result2136_4.nsv"];
val thyn = "vfmTestDefs2136";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

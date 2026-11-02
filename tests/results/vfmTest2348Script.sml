Theory vfmTest2348[no_sig_docs]
Ancestors vfmTestDefs2348
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2348_0.nsv", "result2348_1.nsv", "result2348_2.nsv", "result2348_3.nsv", "result2348_4.nsv", "result2348_5.nsv", "result2348_6.nsv", "result2348_7.nsv"];
val thyn = "vfmTestDefs2348";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

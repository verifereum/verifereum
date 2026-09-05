Theory vfmTest2300[no_sig_docs]
Ancestors vfmTestDefs2300
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2300_0.nsv", "result2300_1.nsv", "result2300_2.nsv", "result2300_3.nsv", "result2300_4.nsv", "result2300_5.nsv", "result2300_6.nsv", "result2300_7.nsv"];
val thyn = "vfmTestDefs2300";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

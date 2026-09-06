Theory vfmTest1769[no_sig_docs]
Ancestors vfmTestDefs1769
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1769_0.nsv", "result1769_1.nsv", "result1769_2.nsv", "result1769_3.nsv", "result1769_4.nsv", "result1769_5.nsv", "result1769_6.nsv", "result1769_7.nsv", "result1769_8.nsv", "result1769_9.nsv", "result1769_10.nsv", "result1769_11.nsv", "result1769_12.nsv", "result1769_13.nsv", "result1769_14.nsv", "result1769_15.nsv"];
val thyn = "vfmTestDefs1769";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

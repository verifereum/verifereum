Theory vfmTest1646[no_sig_docs]
Ancestors vfmTestDefs1646
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1646_0.nsv", "result1646_1.nsv", "result1646_2.nsv", "result1646_3.nsv", "result1646_4.nsv", "result1646_5.nsv", "result1646_6.nsv", "result1646_7.nsv", "result1646_8.nsv", "result1646_9.nsv", "result1646_10.nsv", "result1646_11.nsv", "result1646_12.nsv", "result1646_13.nsv", "result1646_14.nsv", "result1646_15.nsv"];
val thyn = "vfmTestDefs1646";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

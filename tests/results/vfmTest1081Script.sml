Theory vfmTest1081[no_sig_docs]
Ancestors vfmTestDefs1081
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1081_0.nsv", "result1081_1.nsv", "result1081_2.nsv", "result1081_3.nsv", "result1081_4.nsv", "result1081_5.nsv", "result1081_6.nsv", "result1081_7.nsv", "result1081_8.nsv", "result1081_9.nsv", "result1081_10.nsv", "result1081_11.nsv", "result1081_12.nsv", "result1081_13.nsv", "result1081_14.nsv", "result1081_15.nsv", "result1081_16.nsv", "result1081_17.nsv", "result1081_18.nsv", "result1081_19.nsv", "result1081_20.nsv"];
val thyn = "vfmTestDefs1081";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

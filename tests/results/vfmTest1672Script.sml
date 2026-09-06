Theory vfmTest1672[no_sig_docs]
Ancestors vfmTestDefs1672
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1672_0.nsv", "result1672_1.nsv", "result1672_2.nsv", "result1672_3.nsv", "result1672_4.nsv", "result1672_5.nsv", "result1672_6.nsv", "result1672_7.nsv", "result1672_8.nsv", "result1672_9.nsv", "result1672_10.nsv", "result1672_11.nsv", "result1672_12.nsv", "result1672_13.nsv", "result1672_14.nsv", "result1672_15.nsv", "result1672_16.nsv", "result1672_17.nsv", "result1672_18.nsv", "result1672_19.nsv"];
val thyn = "vfmTestDefs1672";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

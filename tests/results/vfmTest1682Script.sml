Theory vfmTest1682[no_sig_docs]
Ancestors vfmTestDefs1682
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1682_0.nsv", "result1682_1.nsv", "result1682_2.nsv", "result1682_3.nsv", "result1682_4.nsv", "result1682_5.nsv", "result1682_6.nsv", "result1682_7.nsv", "result1682_8.nsv", "result1682_9.nsv", "result1682_10.nsv", "result1682_11.nsv", "result1682_12.nsv", "result1682_13.nsv", "result1682_14.nsv", "result1682_15.nsv", "result1682_16.nsv", "result1682_17.nsv", "result1682_18.nsv", "result1682_19.nsv"];
val thyn = "vfmTestDefs1682";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

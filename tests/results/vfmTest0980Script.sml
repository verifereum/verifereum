Theory vfmTest0980[no_sig_docs]
Ancestors vfmTestDefs0980
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0980_0.nsv", "result0980_1.nsv", "result0980_2.nsv", "result0980_3.nsv", "result0980_4.nsv", "result0980_5.nsv", "result0980_6.nsv", "result0980_7.nsv", "result0980_8.nsv", "result0980_9.nsv", "result0980_10.nsv", "result0980_11.nsv", "result0980_12.nsv", "result0980_13.nsv", "result0980_14.nsv", "result0980_15.nsv", "result0980_16.nsv", "result0980_17.nsv", "result0980_18.nsv", "result0980_19.nsv", "result0980_20.nsv"];
val thyn = "vfmTestDefs0980";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

Theory vfmTest0038[no_sig_docs]
Ancestors vfmTestDefs0038
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0038_0.nsv", "result0038_1.nsv", "result0038_2.nsv", "result0038_3.nsv", "result0038_4.nsv", "result0038_5.nsv", "result0038_6.nsv", "result0038_7.nsv", "result0038_8.nsv", "result0038_9.nsv", "result0038_10.nsv", "result0038_11.nsv", "result0038_12.nsv", "result0038_13.nsv", "result0038_14.nsv", "result0038_15.nsv", "result0038_16.nsv", "result0038_17.nsv", "result0038_18.nsv", "result0038_19.nsv", "result0038_20.nsv", "result0038_21.nsv", "result0038_22.nsv", "result0038_23.nsv"];
val thyn = "vfmTestDefs0038";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

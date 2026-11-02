Theory vfmTest0923[no_sig_docs]
Ancestors vfmTestDefs0923
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0923_0.nsv", "result0923_1.nsv", "result0923_2.nsv", "result0923_3.nsv", "result0923_4.nsv", "result0923_5.nsv", "result0923_6.nsv", "result0923_7.nsv", "result0923_8.nsv", "result0923_9.nsv", "result0923_10.nsv", "result0923_11.nsv", "result0923_12.nsv", "result0923_13.nsv", "result0923_14.nsv", "result0923_15.nsv", "result0923_16.nsv", "result0923_17.nsv", "result0923_18.nsv", "result0923_19.nsv", "result0923_20.nsv", "result0923_21.nsv", "result0923_22.nsv", "result0923_23.nsv", "result0923_24.nsv", "result0923_25.nsv", "result0923_26.nsv", "result0923_27.nsv", "result0923_28.nsv", "result0923_29.nsv"];
val thyn = "vfmTestDefs0923";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

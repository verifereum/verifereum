Theory vfmTest0958[no_sig_docs]
Ancestors vfmTestDefs0958
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0958_0.nsv", "result0958_1.nsv", "result0958_2.nsv", "result0958_3.nsv", "result0958_4.nsv", "result0958_5.nsv", "result0958_6.nsv", "result0958_7.nsv", "result0958_8.nsv", "result0958_9.nsv", "result0958_10.nsv", "result0958_11.nsv", "result0958_12.nsv", "result0958_13.nsv", "result0958_14.nsv", "result0958_15.nsv", "result0958_16.nsv", "result0958_17.nsv", "result0958_18.nsv", "result0958_19.nsv", "result0958_20.nsv", "result0958_21.nsv", "result0958_22.nsv", "result0958_23.nsv", "result0958_24.nsv", "result0958_25.nsv", "result0958_26.nsv", "result0958_27.nsv", "result0958_28.nsv", "result0958_29.nsv", "result0958_30.nsv", "result0958_31.nsv", "result0958_32.nsv", "result0958_33.nsv"];
val thyn = "vfmTestDefs0958";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

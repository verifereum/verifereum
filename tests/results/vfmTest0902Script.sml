Theory vfmTest0902[no_sig_docs]
Ancestors vfmTestDefs0902
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0902_0.nsv", "result0902_1.nsv", "result0902_2.nsv", "result0902_3.nsv", "result0902_4.nsv", "result0902_5.nsv", "result0902_6.nsv", "result0902_7.nsv", "result0902_8.nsv", "result0902_9.nsv", "result0902_10.nsv", "result0902_11.nsv", "result0902_12.nsv", "result0902_13.nsv", "result0902_14.nsv", "result0902_15.nsv", "result0902_16.nsv", "result0902_17.nsv", "result0902_18.nsv", "result0902_19.nsv", "result0902_20.nsv", "result0902_21.nsv", "result0902_22.nsv", "result0902_23.nsv", "result0902_24.nsv", "result0902_25.nsv", "result0902_26.nsv", "result0902_27.nsv", "result0902_28.nsv", "result0902_29.nsv", "result0902_30.nsv", "result0902_31.nsv", "result0902_32.nsv", "result0902_33.nsv", "result0902_34.nsv", "result0902_35.nsv"];
val thyn = "vfmTestDefs0902";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

Theory vfmTest0126[no_sig_docs]
Ancestors vfmTestDefs0126
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0126_0.nsv", "result0126_1.nsv", "result0126_2.nsv", "result0126_3.nsv", "result0126_4.nsv", "result0126_5.nsv", "result0126_6.nsv", "result0126_7.nsv", "result0126_8.nsv", "result0126_9.nsv", "result0126_10.nsv", "result0126_11.nsv", "result0126_12.nsv", "result0126_13.nsv", "result0126_14.nsv", "result0126_15.nsv", "result0126_16.nsv", "result0126_17.nsv", "result0126_18.nsv", "result0126_19.nsv", "result0126_20.nsv", "result0126_21.nsv", "result0126_22.nsv", "result0126_23.nsv", "result0126_24.nsv", "result0126_25.nsv", "result0126_26.nsv", "result0126_27.nsv", "result0126_28.nsv", "result0126_29.nsv", "result0126_30.nsv", "result0126_31.nsv", "result0126_32.nsv", "result0126_33.nsv", "result0126_34.nsv", "result0126_35.nsv"];
val thyn = "vfmTestDefs0126";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

Theory vfmTest0756[no_sig_docs]
Ancestors vfmTestDefs0756
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0756_0.nsv", "result0756_1.nsv", "result0756_2.nsv", "result0756_3.nsv", "result0756_4.nsv", "result0756_5.nsv", "result0756_6.nsv", "result0756_7.nsv", "result0756_8.nsv", "result0756_9.nsv", "result0756_10.nsv", "result0756_11.nsv", "result0756_12.nsv", "result0756_13.nsv", "result0756_14.nsv", "result0756_15.nsv", "result0756_16.nsv", "result0756_17.nsv", "result0756_18.nsv", "result0756_19.nsv", "result0756_20.nsv", "result0756_21.nsv", "result0756_22.nsv", "result0756_23.nsv", "result0756_24.nsv", "result0756_25.nsv", "result0756_26.nsv", "result0756_27.nsv", "result0756_28.nsv", "result0756_29.nsv", "result0756_30.nsv", "result0756_31.nsv", "result0756_32.nsv", "result0756_33.nsv", "result0756_34.nsv", "result0756_35.nsv"];
val thyn = "vfmTestDefs0756";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

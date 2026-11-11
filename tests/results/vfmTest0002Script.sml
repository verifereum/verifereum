Theory vfmTest0002[no_sig_docs]
Ancestors vfmTestDefs0002
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0002_0.nsv", "result0002_1.nsv", "result0002_2.nsv", "result0002_3.nsv", "result0002_4.nsv", "result0002_5.nsv", "result0002_6.nsv", "result0002_7.nsv", "result0002_8.nsv", "result0002_9.nsv", "result0002_10.nsv", "result0002_11.nsv", "result0002_12.nsv", "result0002_13.nsv", "result0002_14.nsv", "result0002_15.nsv", "result0002_16.nsv", "result0002_17.nsv", "result0002_18.nsv", "result0002_19.nsv", "result0002_20.nsv", "result0002_21.nsv", "result0002_22.nsv", "result0002_23.nsv", "result0002_24.nsv", "result0002_25.nsv", "result0002_26.nsv", "result0002_27.nsv", "result0002_28.nsv", "result0002_29.nsv", "result0002_30.nsv", "result0002_31.nsv", "result0002_32.nsv", "result0002_33.nsv", "result0002_34.nsv", "result0002_35.nsv", "result0002_36.nsv", "result0002_37.nsv", "result0002_38.nsv", "result0002_39.nsv"];
val thyn = "vfmTestDefs0002";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

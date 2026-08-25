Theory vfmTest0983[no_sig_docs]
Ancestors vfmTestDefs0983
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0983_0.nsv", "result0983_1.nsv", "result0983_2.nsv", "result0983_3.nsv", "result0983_4.nsv", "result0983_5.nsv", "result0983_6.nsv", "result0983_7.nsv", "result0983_8.nsv", "result0983_9.nsv", "result0983_10.nsv", "result0983_11.nsv", "result0983_12.nsv", "result0983_13.nsv", "result0983_14.nsv", "result0983_15.nsv", "result0983_16.nsv", "result0983_17.nsv", "result0983_18.nsv", "result0983_19.nsv", "result0983_20.nsv", "result0983_21.nsv", "result0983_22.nsv", "result0983_23.nsv", "result0983_24.nsv", "result0983_25.nsv", "result0983_26.nsv", "result0983_27.nsv", "result0983_28.nsv", "result0983_29.nsv", "result0983_30.nsv", "result0983_31.nsv", "result0983_32.nsv", "result0983_33.nsv", "result0983_34.nsv", "result0983_35.nsv"];
val thyn = "vfmTestDefs0983";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

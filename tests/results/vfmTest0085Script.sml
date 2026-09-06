Theory vfmTest0085[no_sig_docs]
Ancestors vfmTestDefs0085
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0085_0.nsv", "result0085_1.nsv", "result0085_2.nsv", "result0085_3.nsv", "result0085_4.nsv", "result0085_5.nsv", "result0085_6.nsv", "result0085_7.nsv", "result0085_8.nsv", "result0085_9.nsv", "result0085_10.nsv", "result0085_11.nsv", "result0085_12.nsv", "result0085_13.nsv", "result0085_14.nsv", "result0085_15.nsv", "result0085_16.nsv", "result0085_17.nsv", "result0085_18.nsv", "result0085_19.nsv", "result0085_20.nsv", "result0085_21.nsv", "result0085_22.nsv", "result0085_23.nsv", "result0085_24.nsv", "result0085_25.nsv", "result0085_26.nsv", "result0085_27.nsv", "result0085_28.nsv", "result0085_29.nsv", "result0085_30.nsv", "result0085_31.nsv", "result0085_32.nsv", "result0085_33.nsv", "result0085_34.nsv"];
val thyn = "vfmTestDefs0085";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

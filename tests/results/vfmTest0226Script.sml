Theory vfmTest0226[no_sig_docs]
Ancestors vfmTestDefs0226
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0226_0.nsv", "result0226_1.nsv", "result0226_2.nsv", "result0226_3.nsv", "result0226_4.nsv", "result0226_5.nsv", "result0226_6.nsv", "result0226_7.nsv", "result0226_8.nsv", "result0226_9.nsv", "result0226_10.nsv", "result0226_11.nsv", "result0226_12.nsv", "result0226_13.nsv", "result0226_14.nsv", "result0226_15.nsv", "result0226_16.nsv", "result0226_17.nsv", "result0226_18.nsv", "result0226_19.nsv", "result0226_20.nsv", "result0226_21.nsv", "result0226_22.nsv", "result0226_23.nsv", "result0226_24.nsv", "result0226_25.nsv", "result0226_26.nsv", "result0226_27.nsv", "result0226_28.nsv", "result0226_29.nsv", "result0226_30.nsv", "result0226_31.nsv", "result0226_32.nsv", "result0226_33.nsv"];
val thyn = "vfmTestDefs0226";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

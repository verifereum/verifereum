Theory vfmTest0706[no_sig_docs]
Ancestors vfmTestDefs0706
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0706_0.nsv", "result0706_1.nsv", "result0706_2.nsv", "result0706_3.nsv", "result0706_4.nsv", "result0706_5.nsv", "result0706_6.nsv", "result0706_7.nsv", "result0706_8.nsv", "result0706_9.nsv", "result0706_10.nsv", "result0706_11.nsv", "result0706_12.nsv", "result0706_13.nsv", "result0706_14.nsv", "result0706_15.nsv", "result0706_16.nsv", "result0706_17.nsv", "result0706_18.nsv", "result0706_19.nsv", "result0706_20.nsv", "result0706_21.nsv", "result0706_22.nsv", "result0706_23.nsv", "result0706_24.nsv", "result0706_25.nsv", "result0706_26.nsv", "result0706_27.nsv", "result0706_28.nsv", "result0706_29.nsv"];
val thyn = "vfmTestDefs0706";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

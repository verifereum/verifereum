Theory vfmTest0927[no_sig_docs]
Ancestors vfmTestDefs0927
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0927_0.nsv", "result0927_1.nsv", "result0927_2.nsv", "result0927_3.nsv", "result0927_4.nsv", "result0927_5.nsv", "result0927_6.nsv", "result0927_7.nsv", "result0927_8.nsv", "result0927_9.nsv", "result0927_10.nsv", "result0927_11.nsv", "result0927_12.nsv", "result0927_13.nsv", "result0927_14.nsv", "result0927_15.nsv", "result0927_16.nsv", "result0927_17.nsv", "result0927_18.nsv", "result0927_19.nsv", "result0927_20.nsv", "result0927_21.nsv", "result0927_22.nsv", "result0927_23.nsv"];
val thyn = "vfmTestDefs0927";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

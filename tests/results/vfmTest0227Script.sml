Theory vfmTest0227[no_sig_docs]
Ancestors vfmTestDefs0227
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0227_0.nsv", "result0227_1.nsv", "result0227_2.nsv", "result0227_3.nsv", "result0227_4.nsv", "result0227_5.nsv", "result0227_6.nsv", "result0227_7.nsv", "result0227_8.nsv", "result0227_9.nsv", "result0227_10.nsv", "result0227_11.nsv", "result0227_12.nsv", "result0227_13.nsv", "result0227_14.nsv", "result0227_15.nsv", "result0227_16.nsv", "result0227_17.nsv", "result0227_18.nsv", "result0227_19.nsv", "result0227_20.nsv", "result0227_21.nsv"];
val thyn = "vfmTestDefs0227";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

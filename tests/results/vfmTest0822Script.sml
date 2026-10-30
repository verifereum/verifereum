Theory vfmTest0822[no_sig_docs]
Ancestors vfmTestDefs0822
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0822_0.nsv", "result0822_1.nsv", "result0822_2.nsv", "result0822_3.nsv", "result0822_4.nsv", "result0822_5.nsv", "result0822_6.nsv", "result0822_7.nsv", "result0822_8.nsv", "result0822_9.nsv", "result0822_10.nsv", "result0822_11.nsv", "result0822_12.nsv", "result0822_13.nsv", "result0822_14.nsv", "result0822_15.nsv", "result0822_16.nsv", "result0822_17.nsv", "result0822_18.nsv", "result0822_19.nsv"];
val thyn = "vfmTestDefs0822";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

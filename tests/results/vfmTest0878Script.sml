Theory vfmTest0878[no_sig_docs]
Ancestors vfmTestDefs0878
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0878_0.nsv", "result0878_1.nsv", "result0878_2.nsv", "result0878_3.nsv", "result0878_4.nsv", "result0878_5.nsv", "result0878_6.nsv", "result0878_7.nsv", "result0878_8.nsv", "result0878_9.nsv", "result0878_10.nsv", "result0878_11.nsv", "result0878_12.nsv", "result0878_13.nsv", "result0878_14.nsv", "result0878_15.nsv", "result0878_16.nsv", "result0878_17.nsv", "result0878_18.nsv", "result0878_19.nsv", "result0878_20.nsv", "result0878_21.nsv", "result0878_22.nsv", "result0878_23.nsv"];
val thyn = "vfmTestDefs0878";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

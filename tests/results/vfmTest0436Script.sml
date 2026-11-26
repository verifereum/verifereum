Theory vfmTest0436[no_sig_docs]
Ancestors vfmTestDefs0436
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0436_0.nsv", "result0436_1.nsv", "result0436_2.nsv", "result0436_3.nsv", "result0436_4.nsv", "result0436_5.nsv", "result0436_6.nsv", "result0436_7.nsv", "result0436_8.nsv", "result0436_9.nsv", "result0436_10.nsv", "result0436_11.nsv", "result0436_12.nsv", "result0436_13.nsv", "result0436_14.nsv", "result0436_15.nsv", "result0436_16.nsv", "result0436_17.nsv", "result0436_18.nsv", "result0436_19.nsv", "result0436_20.nsv", "result0436_21.nsv", "result0436_22.nsv", "result0436_23.nsv", "result0436_24.nsv", "result0436_25.nsv", "result0436_26.nsv"];
val thyn = "vfmTestDefs0436";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

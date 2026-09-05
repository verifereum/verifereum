Theory vfmTest2294[no_sig_docs]
Ancestors vfmTestDefs2294
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2294_0.nsv", "result2294_1.nsv", "result2294_2.nsv", "result2294_3.nsv", "result2294_4.nsv", "result2294_5.nsv", "result2294_6.nsv", "result2294_7.nsv", "result2294_8.nsv", "result2294_9.nsv", "result2294_10.nsv", "result2294_11.nsv", "result2294_12.nsv", "result2294_13.nsv", "result2294_14.nsv", "result2294_15.nsv", "result2294_16.nsv", "result2294_17.nsv", "result2294_18.nsv", "result2294_19.nsv", "result2294_20.nsv", "result2294_21.nsv", "result2294_22.nsv", "result2294_23.nsv"];
val thyn = "vfmTestDefs2294";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

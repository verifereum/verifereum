Theory vfmTest2937[no_sig_docs]
Ancestors vfmTestDefs2937
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2937_0.nsv", "result2937_1.nsv", "result2937_2.nsv", "result2937_3.nsv", "result2937_4.nsv", "result2937_5.nsv", "result2937_6.nsv", "result2937_7.nsv", "result2937_8.nsv", "result2937_9.nsv", "result2937_10.nsv", "result2937_11.nsv", "result2937_12.nsv", "result2937_13.nsv", "result2937_14.nsv", "result2937_15.nsv", "result2937_16.nsv"];
val thyn = "vfmTestDefs2937";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

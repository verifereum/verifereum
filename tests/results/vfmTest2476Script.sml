Theory vfmTest2476[no_sig_docs]
Ancestors vfmTestDefs2476
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2476_0.nsv", "result2476_1.nsv", "result2476_2.nsv", "result2476_3.nsv", "result2476_4.nsv", "result2476_5.nsv", "result2476_6.nsv", "result2476_7.nsv", "result2476_8.nsv", "result2476_9.nsv", "result2476_10.nsv", "result2476_11.nsv", "result2476_12.nsv", "result2476_13.nsv", "result2476_14.nsv", "result2476_15.nsv", "result2476_16.nsv", "result2476_17.nsv"];
val thyn = "vfmTestDefs2476";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

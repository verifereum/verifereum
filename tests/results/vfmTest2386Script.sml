Theory vfmTest2386[no_sig_docs]
Ancestors vfmTestDefs2386
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2386_0.nsv", "result2386_1.nsv", "result2386_2.nsv", "result2386_3.nsv", "result2386_4.nsv", "result2386_5.nsv", "result2386_6.nsv", "result2386_7.nsv", "result2386_8.nsv", "result2386_9.nsv", "result2386_10.nsv", "result2386_11.nsv", "result2386_12.nsv", "result2386_13.nsv", "result2386_14.nsv", "result2386_15.nsv", "result2386_16.nsv", "result2386_17.nsv", "result2386_18.nsv", "result2386_19.nsv"];
val thyn = "vfmTestDefs2386";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

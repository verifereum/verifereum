Theory vfmTest2380[no_sig_docs]
Ancestors vfmTestDefs2380
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2380_0.nsv", "result2380_1.nsv", "result2380_2.nsv", "result2380_3.nsv", "result2380_4.nsv", "result2380_5.nsv", "result2380_6.nsv", "result2380_7.nsv"];
val thyn = "vfmTestDefs2380";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

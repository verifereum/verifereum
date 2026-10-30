Theory vfmTest2482[no_sig_docs]
Ancestors vfmTestDefs2482
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2482_0.nsv", "result2482_1.nsv", "result2482_2.nsv", "result2482_3.nsv", "result2482_4.nsv", "result2482_5.nsv", "result2482_6.nsv", "result2482_7.nsv", "result2482_8.nsv", "result2482_9.nsv", "result2482_10.nsv", "result2482_11.nsv", "result2482_12.nsv", "result2482_13.nsv", "result2482_14.nsv", "result2482_15.nsv"];
val thyn = "vfmTestDefs2482";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

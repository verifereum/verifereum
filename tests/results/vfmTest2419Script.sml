Theory vfmTest2419[no_sig_docs]
Ancestors vfmTestDefs2419
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2419_0.nsv", "result2419_1.nsv", "result2419_2.nsv", "result2419_3.nsv", "result2419_4.nsv", "result2419_5.nsv", "result2419_6.nsv", "result2419_7.nsv"];
val thyn = "vfmTestDefs2419";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

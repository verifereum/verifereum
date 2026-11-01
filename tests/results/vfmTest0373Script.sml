Theory vfmTest0373[no_sig_docs]
Ancestors vfmTestDefs0373
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0373_0.nsv", "result0373_1.nsv", "result0373_2.nsv", "result0373_3.nsv", "result0373_4.nsv", "result0373_5.nsv", "result0373_6.nsv", "result0373_7.nsv", "result0373_8.nsv", "result0373_9.nsv", "result0373_10.nsv", "result0373_11.nsv"];
val thyn = "vfmTestDefs0373";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

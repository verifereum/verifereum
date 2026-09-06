Theory vfmTest1648[no_sig_docs]
Ancestors vfmTestDefs1648
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1648_0.nsv", "result1648_1.nsv", "result1648_2.nsv", "result1648_3.nsv", "result1648_4.nsv", "result1648_5.nsv", "result1648_6.nsv", "result1648_7.nsv", "result1648_8.nsv", "result1648_9.nsv", "result1648_10.nsv", "result1648_11.nsv"];
val thyn = "vfmTestDefs1648";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

Theory vfmTest0289[no_sig_docs]
Ancestors vfmTestDefs0289
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0289_0.nsv", "result0289_1.nsv", "result0289_2.nsv", "result0289_3.nsv", "result0289_4.nsv", "result0289_5.nsv", "result0289_6.nsv", "result0289_7.nsv", "result0289_8.nsv", "result0289_9.nsv", "result0289_10.nsv", "result0289_11.nsv"];
val thyn = "vfmTestDefs0289";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

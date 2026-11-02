Theory vfmTest0937[no_sig_docs]
Ancestors vfmTestDefs0937
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0937_0.nsv", "result0937_1.nsv", "result0937_2.nsv", "result0937_3.nsv", "result0937_4.nsv", "result0937_5.nsv", "result0937_6.nsv", "result0937_7.nsv", "result0937_8.nsv"];
val thyn = "vfmTestDefs0937";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

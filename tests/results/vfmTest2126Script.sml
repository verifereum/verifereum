Theory vfmTest2126[no_sig_docs]
Ancestors vfmTestDefs2126
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2126_0.nsv", "result2126_1.nsv", "result2126_2.nsv", "result2126_3.nsv", "result2126_4.nsv", "result2126_5.nsv"];
val thyn = "vfmTestDefs2126";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

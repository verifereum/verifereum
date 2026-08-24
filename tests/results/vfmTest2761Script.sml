Theory vfmTest2761[no_sig_docs]
Ancestors vfmTestDefs2761
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2761_0.nsv", "result2761_1.nsv", "result2761_2.nsv", "result2761_3.nsv"];
val thyn = "vfmTestDefs2761";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

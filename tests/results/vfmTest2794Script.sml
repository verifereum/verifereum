Theory vfmTest2794[no_sig_docs]
Ancestors vfmTestDefs2794
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2794_0.nsv", "result2794_1.nsv", "result2794_2.nsv", "result2794_3.nsv"];
val thyn = "vfmTestDefs2794";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

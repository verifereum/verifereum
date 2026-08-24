Theory vfmTest2684[no_sig_docs]
Ancestors vfmTestDefs2684
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2684_0.nsv", "result2684_1.nsv", "result2684_2.nsv", "result2684_3.nsv"];
val thyn = "vfmTestDefs2684";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

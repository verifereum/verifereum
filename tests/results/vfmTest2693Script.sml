Theory vfmTest2693[no_sig_docs]
Ancestors vfmTestDefs2693
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2693_0.nsv", "result2693_1.nsv", "result2693_2.nsv", "result2693_3.nsv"];
val thyn = "vfmTestDefs2693";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

Theory vfmTest2770[no_sig_docs]
Ancestors vfmTestDefs2770
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2770_0.nsv", "result2770_1.nsv", "result2770_2.nsv", "result2770_3.nsv"];
val thyn = "vfmTestDefs2770";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

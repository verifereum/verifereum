Theory vfmTest0011[no_sig_docs]
Ancestors vfmTestDefs0011
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0011_0.nsv", "result0011_1.nsv", "result0011_2.nsv", "result0011_3.nsv", "result0011_4.nsv", "result0011_5.nsv", "result0011_6.nsv", "result0011_7.nsv"];
val thyn = "vfmTestDefs0011";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

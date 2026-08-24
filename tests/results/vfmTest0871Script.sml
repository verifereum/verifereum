Theory vfmTest0871[no_sig_docs]
Ancestors vfmTestDefs0871
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0871_0.nsv", "result0871_1.nsv", "result0871_2.nsv", "result0871_3.nsv"];
val thyn = "vfmTestDefs0871";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
